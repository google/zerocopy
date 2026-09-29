#!/usr/bin/env python3
"""Check discriminating retained observations; not a fresh Lake replay."""
import json
from pathlib import Path

r = json.loads((Path(__file__).parent / "results.json").read_text())
assert r["revision"] == "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"
assert len(r["runs"]) == 21
run = {x["label"]: x for x in r["runs"]}
assert len(run) == len(r["runs"])
for label in ("base-build", "base-replay", "base-no-build", "base-setup",
              "assigned-name-alias-build", "assigned-name-alias-setup",
              "dependency-index-shift-build", "dependency-index-shift-setup",
              "relative-root-build", "relative-root-setup", "K-first", "K-second",
              "server-option-changed-setup", "changed-source-build-rehash",
              "changed-source-post-build-replay",
              "transitive-name-ab-manifest-a-build",
              "transitive-name-ba-manifest-a-build",
              "transitive-name-ab-manifest-b-build"):
    assert run[label]["exit"] == 0, label
assert run["changed-source-no-build-rehash"]["exit"] == 3
for order in ("ab", "ba"):
    x = run[f"duplicate-name-{order}-build"]
    assert x["exit"] == 1
    assert "`probe_dep` has already been declared" in x["stderr"]
    assert not any(k.startswith("duplicate/producer_") for k in x["delta"]["added"])
assert "info: Generated.lean:2:0: 7" in run["transitive-name-ab-manifest-a-build"]["stdout"]
assert "info: Generated.lean:2:0: 7" in run["transitive-name-ba-manifest-a-build"]["stdout"]
assert "info: Generated.lean:2:0: 9" in run["transitive-name-ab-manifest-b-build"]["stdout"]
assert "duplicate/producer_a/.lake/build/lib/lean/Dep.olean" in run["transitive-name-ab-manifest-a-build"]["delta"]["added"]
assert "duplicate/producer_b/.lake/build/lib/lean/Dep.olean" in run["transitive-name-ab-manifest-b-build"]["delta"]["added"]
assert "Built Dep" in run["base-build"]["stdout"]
assert "Replayed Dep" in run["base-replay"]["stdout"]
assert "Replayed Dep" in run["assigned-name-alias-build"]["stdout"]
assert "Replayed Dep" in run["dependency-index-shift-build"]["stdout"]
assert "Built Dep" in run["changed-source-build-rehash"]["stdout"]
assert "Replayed Dep" in run["changed-source-post-build-replay"]["stdout"]
assert "$TOOLCHAIN_BIN/lean" in run["base-build"]["observed_descendants"]
assert "$TOOLCHAIN_BIN/lean" in run["changed-source-build-rehash"]["observed_descendants"]
assert not run["base-replay"]["observed_descendants"]
assert not run["changed-source-post-build-replay"]["observed_descendants"]
assert not any(run["base-replay"]["delta"].values())
assert "producer/.lake/config/dep_alias/lakefile.olean.trace" in run["assigned-name-alias-build"]["delta"]["added"]
assert "producer/.lake/config/probe_dep/lakefile.olean.trace" in run["dependency-index-shift-build"]["delta"]["content_changed"]
assert "producer/.lake/config/probe_dep/lakefile.olean.trace" in run["relative-root-build"]["delta"]["content_changed"]
assert "producer/.lake/build/lib/lean/Dep.trace.nobuild" in run["changed-source-no-build-rehash"]["delta"]["added"]
assert "producer/.lake/build/lib/lean/Dep.olean" in run["changed-source-build-rehash"]["delta"]["content_changed"]
s = r["snapshots"]
name = ".lake/config/probe_dep/lakefile.olean.trace"
alias = ".lake/config/dep_alias/lakefile.olean.trace"
assert s["base_config_traces"][name]["idx"] == 1
assert s["alias_config_traces"][alias]["name"] == "dep_alias"
assert s["shift_config_traces"][name]["idx"] == 2
assert s["relative_root_config_traces"][name]["idx"] == 1
assert all(x["leanHash"] == r["revision"]
           for key in ("base_config_traces", "alias_config_traces",
                       "shift_config_traces", "relative_root_config_traces")
           for x in s[key].values())
print("retained Lake matrix checks passed")
