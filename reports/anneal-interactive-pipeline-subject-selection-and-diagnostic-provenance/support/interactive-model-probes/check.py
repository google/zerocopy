#!/usr/bin/env python3
"""Read-only checks for the retained finite-model and APFS fixture results."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parent
model = json.loads((root / "model-probes.json").read_text())
pubroot = root / "publication-fixture"
publication = json.loads((pubroot / "publication-probe.json").read_text())
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
identity = json.loads((root.parent / "REPORT.json").read_text())["subjects"][0]["identity"]
assert identity["model_probes_sha256"] == sha(root / "model_probes.py")
assert identity["publication_probe_sha256"] == sha(root / "publication_probe.py")
subprocess.run([sys.executable, str(root / "model_probes.py"), "--check"], check=True)
subprocess.run([sys.executable, str(root / "supersession_gap_probe.py"), "--check"], check=True)
gap = json.loads((root / "supersession-gap.json").read_text())
assert gap["valid_orders"] == 10
assert gap["delayed_stage_token_stale_publishes"] == 2
assert gap["request_time_token_stale_publishes"] == 0
assert gap["delayed_stage_token_accepted_publications"] == 13
assert gap["request_time_token_accepted_publications"] == 11
assert gap["stale_gap_orders"] == [
    ["stageA", "requestB", "publishA", "stageB", "publishB"],
    ["requestB", "stageA", "publishA", "stageB", "publishB"],
]

identity_cases = model["identity_ablation"]
assert len(identity_cases["cases"]) == 10
assert len({tuple(c["changed_fields"]) for c in identity_cases["cases"]}) == 10
assert all(c["full_causal_identity_changes"] for c in identity_cases["cases"])
assert "path" in identity_cases["cases"][0]["insufficient_keys_colliding"]
assert "uri_version" in identity_cases["cases"][1]["insufficient_keys_colliding"]
assert "proof_hash" in identity_cases["cases"][2]["insufficient_keys_colliding"]
aba = identity_cases["cache_content_identity_example"]
assert aba["a_to_b_content_changes"] and aba["a_to_b_to_a_content_recurs"]
assert aba["causal_tags_all_distinct"]
assert aba["content_keys"][0] == aba["content_keys"][2] != aba["content_keys"][1]
assert len({tuple(tag) for tag in aba["causal_tags"]}) == 3

projection = model["projection_coordinates"]
assert projection["corpus_strings"] == 59
assert projection["valid_scalar_boundaries_checked"] == 2092
assert projection["all_utf8_utf16_roundtrips"]
assert [x["name"] for x in projection["patch_cases"]] == [
    "inside one segment", "touches synthetic prefix", "crosses synthetic gap",
    "stale host digest", "stale projection digest", "stale document version",
]
assert [x["accepted"] for x in projection["patch_cases"]] == [True, False, False, False, False, False]
assert projection["stale_patch_cas_rejected"]
schedules = model["generation_schedule_model"]
assert schedules["permutations"] == 120
assert schedules["stale_publish_rejections"] == 10
assert schedules["naive_late_publish_counterexample_count"] == 10
assert schedules["safe_stale_publishes"] == 0
assert schedules["safe_current_generation_guard"]
assert schedules["counterexample_orders"]

assert (pubroot / "current").is_symlink()
assert (pubroot / "current").readlink() == Path("gen-B")
for label, field in (("gen-A", "generation_a_sha256"), ("gen-B", "generation_b_sha256")):
    assert {p.name: sha(p) for p in (pubroot / label).iterdir()} == publication[field]
assert (pubroot / "gen-C/Types.lean").is_file()
assert not (pubroot / "gen-C/Funs.lean").exists()
assert publication["un-pinned_reader_interleaving"]["mixed_generation_observed"]
assert publication["un-pinned_reader_interleaving"]["first_file"] == "-- generation gen-A"
assert publication["un-pinned_reader_interleaving"]["second_file_after_swap"] == "-- generation gen-B"
assert publication["un-pinned_reader_interleaving"]["manifest_generation_after_swap"] == "gen-B"
assert publication["pinned_reader"]["consistent_old_generation"]
assert publication["pinned_reader"]["first_file"] == publication["pinned_reader"]["second_file_after_swap"] == "-- generation gen-A"
incomplete = publication["incomplete_stage"]
assert incomplete["visible_generation_before"] == "gen-B"
assert incomplete["forced_current"] == "gen-C"
assert incomplete["forced_publish_missing_file"]
assert incomplete["visible_state_before_forced_swap"] == ["-- generation gen-B", "-- generation gen-B", "gen-B", "olean:gen-B"]
assert incomplete["restored_current"] == "gen-B"
assert not incomplete["published_incomplete_at_end"]
assert publication["old_generation_retained_after_swap"]

print("PASS: fresh model replay, 10 identity cases, explicit A→B→A, 2,092 boundaries, 120 schedules, APFS publication controls")
