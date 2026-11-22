#!/usr/bin/env python3
"""Check that source lines quoted by the report exist at the pinned revisions.

`source_anchors.json` lists, per repository revision and file, the exact text
of quoted lines together with their 1-based line numbers.  This script fetches
each file from raw.githubusercontent.com at the pinned commit and reports any
anchor whose line no longer carries that text (after trimming whitespace).

Usage:
  python3 check_source_anchors.py [--anchors source_anchors.json] [--root DIR]

With --root, files are read from DIR/<owner>/<repo>/<sha>/<path> instead of
the network (useful with a local mirror).  Network fetches use urllib and
fall back to `curl` if it is installed.  Exit status 0 iff every reachable
anchor matches; unreachable files are listed and do not fail the run.
"""
import argparse
import http.client
import json
import os
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request


def fetch(repo, sha, path, root):
    if root:
        with open(os.path.join(root, repo, sha, path), encoding="utf-8") as f:
            return f.read()
    url = "https://raw.githubusercontent.com/%s/%s/%s" % (repo, sha, path)
    last = None
    curl = shutil.which("curl")
    for attempt in range(1 if curl else 3):
        try:
            with urllib.request.urlopen(url, timeout=60) as r:
                return r.read().decode("utf-8")
        except urllib.error.HTTPError:
            raise                      # 404 etc.: not transient
        except (OSError, http.client.HTTPException) as e:
            last = e
            if not curl:
                time.sleep(1 + attempt)
    # Some proxies drop urllib connections; fall back to curl when present.
    if curl:
        p = subprocess.run([curl, "-sS", "-f", "-L", "-m", "60", url], capture_output=True)
        if p.returncode == 0:
            return p.stdout.decode("utf-8")
        last = OSError("curl exit %d: %s" % (p.returncode, p.stderr.decode("utf-8", "replace").strip()[:120]))
    raise OSError("fetch failed: %r" % (last,))


def main():
    ap = argparse.ArgumentParser()
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("--anchors", default=os.path.join(here, "source_anchors.json"))
    ap.add_argument("--root", default=None)
    args = ap.parse_args()
    data = json.load(open(args.anchors, encoding="utf-8"))
    bad = unreachable = ok = 0
    for ent in data["files"]:
        repo, sha, path = ent["repository"], ent["revision"], ent["path"]
        try:
            lines = fetch(repo, sha, path, args.root).splitlines()
        except (OSError, urllib.error.URLError) as e:
            unreachable += 1
            print("UNREACHABLE %s@%s:%s (%s)" % (repo, sha[:12], path, e.__class__.__name__))
            continue
        for a in ent["anchors"]:
            n, text = a["line"], a["text"]
            got = lines[n - 1].strip() if 0 < n <= len(lines) else None
            if got == text:
                ok += 1
            else:
                bad += 1
                print("MISMATCH %s@%s:%s:%d\n  want: %s\n  got:  %s" % (repo, sha[:12], path, n, text, got))
    print("anchors ok=%d mismatched=%d unreachable_files=%d" % (ok, bad, unreachable))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
