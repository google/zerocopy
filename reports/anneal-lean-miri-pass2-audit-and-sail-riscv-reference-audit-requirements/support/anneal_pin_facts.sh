#!/usr/bin/env bash
# Reproduce the joshlf/anneal Pass 2 pin facts quoted in REPORT.md.
# Usage: anneal_pin_facts.sh <path-to-anneal-clone>   (needs commit c131b320 fetched)
set -euo pipefail
A="$1"; S=c131b320eeeb26ef692e5afd5ec8db49ee518613
cd "$A"
echo "pin sha256: $(git show $S:vendor/lean-miri/UPSTREAM_PIN.json | sha256sum | cut -c1-64)"
git show $S:trusted/audit/src/lib.rs | grep -A1 -E 'pub const LOCKED_(UPSTREAM_PIN_SHA256|MIRI_COMMIT)' | tr -s ' '
git show $S:vendor/lean-miri/UPSTREAM_PIN.json | python3 -c '
import json,sys,collections
d=json.load(sys.stdin)
print("keys:", sorted(d))
print("schema_version:", d["schema_version"], "commit:", d["commit"])
print("upstream_lean_toolchain:", d["upstream_lean_toolchain"], "build_lean_toolchain:", d["build_lean_toolchain"])
c=d["execution_machine_closure"]
print("closure entries:", len(c), "first:", c[0]["module"], "last:", c[-1]["module"])
print("entries with server/private sidecars:", [e["module"] for e in c if "olean_server_sha256" in e])
print("closure by top namespace:", dict(collections.Counter(e["module"].split(".")[1] for e in c)))
print("patched_files:", [p["path"] for p in d["patched_files"]])
print("vendor_tree.file_count:", d["vendor_tree"]["file_count"], "manifest_sha256:", d["vendor_tree"]["manifest_sha256"])
' 
paths=$(git show $S:vendor/lean-miri/UPSTREAM_PIN.json | python3 -c 'import json,sys; print(" ".join("vendor/lean-miri/"+e["path"] for e in json.load(sys.stdin)["execution_machine_closure"]))')
echo "closure LOC: $(for p in $paths; do git show $S:$p; done | wc -l)"
echo "all vendored .lean LOC: $(for p in $(git ls-tree -r --name-only $S vendor/lean-miri | grep '\.lean$'); do git show $S:$p; done | wc -l)"
for pat in '^\s*(private |protected )?partial def' '@\[extern' '@\[implemented_by' '^\s*axiom ' '^\s*(private )?opaque ' '\bsorry\b' 'native_decide' '^\s*run_cmd' '^\s*initialize '; do
  n=$( { git grep -c -E "$pat" $S -- $paths 2>/dev/null || true; } | awk -F: '{s+=$NF} END{print s+0}')
  echo "closure count [$pat]: $n"
done
