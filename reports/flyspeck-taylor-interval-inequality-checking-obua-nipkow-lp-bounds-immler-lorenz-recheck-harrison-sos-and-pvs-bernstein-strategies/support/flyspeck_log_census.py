#!/usr/bin/env python3
"""Re-derive per-run verification-time totals from the nonlinear-inequality
run logs committed to the flyspeck/flyspeck repository.

Inputs: the per-batch `stdout` files under `azure/results/` at a pinned commit
(fetched from raw.githubusercontent.com) and the digest list in
`text_formalization/general/theorem_nonlinear_digest.hl`.

Each verifier process prints, per inequality case, a line of the form
    Time <id>: <seconds>
where <seconds> is `total_time` from formal_ineqs' `verify_ineq` (certificate
search + informal precision search + formal replay; it excludes the
per-process HOL Light loading time, which is printed separately as
`Loading time: <seconds>` by newer batches).

Usage:
    python3 flyspeck_log_census.py [workdir]      # default workdir /tmp/flyspeck-logs
Standard library only. Network: GitHub API + raw.githubusercontent.com.
"""
import collections
import concurrent.futures
import json
import os
import re
import statistics
import sys
import urllib.request

REPO = "flyspeck/flyspeck"
SHA = "32948714cdf06d700af2c993c9a92b7b551d7af5"
UA = {"User-Agent": "research-bot"}
WORK = sys.argv[1] if len(sys.argv) > 1 else "/tmp/flyspeck-logs"
KEEP = re.compile(r"^(Time|Hash|FAILURE|ERROR|WARNING|Loading time)")


def get(url):
    req = urllib.request.Request(url, headers=UA)
    with urllib.request.urlopen(req, timeout=120) as r:
        return r.read()


def fetch(path):
    out = os.path.join(WORK, "x", path.replace("azure/results/", "").replace("/", "__"))
    if os.path.exists(out):
        return out
    body = get(f"https://raw.githubusercontent.com/{REPO}/{SHA}/{path}").decode("utf-8", "replace")
    kept = [l for l in body.splitlines() if KEEP.match(l)]
    with open(out + ".tmp", "w") as f:
        f.write("\n".join(kept) + "\n__EOF__\n")
    os.replace(out + ".tmp", out)
    return out


def main():
    os.makedirs(os.path.join(WORK, "x"), exist_ok=True)
    tree = json.loads(get(f"https://api.github.com/repos/{REPO}/git/trees/{SHA}?recursive=1"))
    assert not tree.get("truncated"), "tree listing truncated"
    paths = [e["path"] for e in tree["tree"] if e["type"] == "blob" and (
        e["path"].startswith("azure/results/output/")
        or e["path"].startswith("azure/results/out-extra/")
        or e["path"].startswith("azure/results/urban/out/"))]
    with concurrent.futures.ThreadPoolExecutor(12) as ex:
        files = list(ex.map(fetch, paths))

    def norm(case_id):  # newer batches prefix the id with "<case number>,"
        return re.sub(r"^\d+,", "", case_id.strip())

    run_of = lambda f: "second-run(urban/out)" if os.path.basename(f).startswith("urban__") else "first-run(output+out-extra)"
    per_run = collections.defaultdict(dict)
    stats = collections.defaultdict(lambda: collections.Counter())
    loads = collections.defaultdict(list)
    for f in files:
        r = run_of(f)
        stats[r]["files"] += 1
        for line in open(f):
            m = re.match(r"^Time\s+(.*):\s*([0-9.]+)$", line.strip())
            if m:
                per_run[r][norm(m.group(1))] = per_run[r].get(norm(m.group(1)), 0.0) + float(m.group(2))
            elif line.startswith("FAILURE"):
                stats[r]["FAILURE lines"] += 1
            elif line.startswith("ERROR"):
                stats[r]["ERROR lines"] += 1
            elif line.startswith("Loading time"):
                loads[r].append(float(line.split(":")[1]))

    digest_body = get(f"https://raw.githubusercontent.com/{REPO}/{SHA}/text_formalization/general/theorem_nonlinear_digest.hl").decode()
    digest = set(re.findall(r'^\("(.*):", "[0-9a-f]{32}"\);', digest_body, re.M))

    print(f"repository {REPO} @ {SHA}")
    print(f"log files fetched: {len(files)}")
    print(f"digest entries (theorem_nonlinear_digest.hl): {len(digest)}")
    for r in sorted(per_run):
        t = sorted(per_run[r].values())
        tot = sum(t)
        p99 = t[int(0.99 * (len(t) - 1))]
        ld = loads[r]
        print(f"\n[{r}]")
        print(f"  stdout files            : {stats[r]['files']}")
        print(f"  distinct cases with Time: {len(t)}")
        print(f"  sum of per-case Time    : {tot:.0f} s = {tot/3600:.1f} h")
        print(f"  median / p99 / max case : {statistics.median(t):.1f} s / {p99:.1f} s / {t[-1]:.1f} s")
        print(f"  FAILURE / ERROR lines   : {stats[r]['FAILURE lines']} / {stats[r]['ERROR lines']} (failed cases were re-run in later batches)")
        if ld:
            print(f"  'Loading time' lines    : {len(ld)}, mean {statistics.mean(ld):.1f} s, sum {sum(ld)/3600:.1f} h")
        print(f"  cases also in digest    : {len(digest & set(per_run[r]))}")
    runs = sorted(per_run)
    if len(runs) == 2:
        a, b = (per_run[x] for x in runs)
        common = set(a) & set(b)
        print(f"\ncases common to both runs: {len(common)}")
        print(f"digest entries in neither run: {sorted(digest - set(a) - set(b))}")


if __name__ == "__main__":
    main()
