#!/usr/bin/env python3
"""Controlled annotation, regeneration, edit-action, and Lean layout probes.

The //% grammar and projector are invented for this experiment. They are not
Anneal implementation code. The script writes only raw-results.json beside it.
"""

import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
LEAN = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean")
RUSTC = Path(os.environ.get("RUSTC", "rustc"))


def sha(data):
    if isinstance(data, str):
        data = data.encode()
    return hashlib.sha256(data).hexdigest()


def scan(source):
    """Line scanner: exact byte intervals, no Rust parse or subject attachment."""
    lines = source.splitlines(keepends=True)
    blocks = []
    active = None
    offset = 0
    for line in lines:
        content = line.rstrip("\r\n")
        begin = re.fullmatch(r"//% begin ([a-z][a-z0-9]*)", content)
        if begin and active is None:
            active = {"id": begin.group(1), "start": offset, "segments": [], "complete": False}
        elif content == "//% end" and active is not None:
            active["complete"] = True
            active["end"] = offset + len(line)
            blocks.append(active)
            active = None
        elif active is not None:
            match = re.match(r"//% ?", line)
            if match:
                start = offset + match.end()
                active["segments"].append([start, offset + len(line)])
            else:
                # Preserve the text, but do not assign edit authority to it.
                active["segments"].append(None)
        offset += len(line)
    if active is not None:
        active["end"] = len(source)
        blocks.append(active)
    return blocks


def render(source):
    blocks = scan(source)
    out = "-- synthetic header\n"
    mapping = []
    for block in blocks:
        if not block["complete"] or any(s is None for s in block["segments"]):
            continue
        out += f"namespace P_{block['id']}\n"
        for start, end in block["segments"]:
            piece = source[start:end]
            mapping.append({"out": [len(out), len(out) + len(piece)], "source": [start, end], "id": block["id"]})
            out += piece
        out += f"end P_{block['id']}\n"
    return out, mapping


def apply_action(source, expected_source_hash, expected_projection_hash, expected_version, version, edits):
    projection, mapping = render(source)
    if sha(source) != expected_source_hash or sha(projection) != expected_projection_hash or version != expected_version:
        return {"ok": False, "reason": "stale-generation", "source": source}
    mapped = []
    for edit in edits:
        if edit.get("format", "plain") != "plain":
            return {"ok": False, "reason": "unsupported-snippet", "source": source}
        a, b = edit["range"]
        if a >= b or a < 0 or b > len(projection):
            return {"ok": False, "reason": "bad-range", "source": source}
        owners = [m for m in mapping if m["out"][0] <= a and b <= m["out"][1]]
        if len(owners) != 1:
            return {"ok": False, "reason": "no-single-authored-origin", "source": source}
        m = owners[0]
        lo = m["source"][0] + a - m["out"][0]
        hi = m["source"][0] + b - m["out"][0]
        if source[lo:hi] != edit["expected"] or projection[a:b] != edit["expected"]:
            return {"ok": False, "reason": "expected-bytes-mismatch", "source": source}
        mapped.append((lo, hi, edit["replacement"]))
    ordered = sorted(mapped)
    if any(ordered[i][1] > ordered[i + 1][0] for i in range(len(ordered) - 1)):
        return {"ok": False, "reason": "overlap", "source": source}
    for lo, hi, replacement in reversed(ordered):
        source = source[:lo] + replacement + source[hi:]
    return {"ok": True, "reason": "applied-atomically", "source": source}


def command(argv, cwd):
    proc = subprocess.run([str(x) for x in argv], cwd=cwd, text=True, capture_output=True, timeout=30)
    canon = lambda s: s.replace(str(cwd), "$WORK")
    return {"argv": [canon(str(x)) for x in argv], "exit": proc.returncode, "stdout": canon(proc.stdout), "stderr": canon(proc.stderr)}


def main():
    assert LEAN.exists(), LEAN
    with tempfile.TemporaryDirectory(prefix="annotation-gap-") as tmp:
        tmp = Path(tmp)
        baseline = (
            "pub fn f() -> u32 { 7 }\r\n"
            "//% begin a\r\n"
            "//% theorem helper : True := by trivial\r\n"
            "//% theorem proof : True := by exact helper\r\n"
            "//% end\r\n"
        )
        buffer = baseline.replace("exact helper", "  exact helper -- retained spacing")
        changed_rust = buffer.replace("{ 7 }", "{ 9 }")
        incomplete = baseline.replace("pub fn f() -> u32 { 7 }", "pub fn f( -> u32 { 7 }")
        unclosed = baseline.replace("//% end\r\n", "")
        malformed_line = baseline.replace("//% theorem helper", "// theorem helper")

        fixture = {}
        for name, source in [("baseline", baseline), ("unsaved_buffer", buffer), ("rust_body_changed", changed_rust), ("rust_incomplete", incomplete), ("unclosed_annotation", unclosed), ("malformed_annotation_line", malformed_line)]:
            projected, mapping = render(source)
            rust_file = tmp / f"{name}.rs"
            rust_file.write_bytes(source.encode())
            rust = command([RUSTC, "--crate-type", "lib", "--emit", "metadata", "--out-dir", tmp, rust_file], tmp)
            fixture[name] = {"source": source, "source_sha256": sha(source), "blocks": scan(source), "projection": projected, "projection_sha256": sha(projected), "map": mapping, "rustc": rust}
        assert fixture["baseline"]["rustc"]["exit"] == 0
        assert fixture["rust_incomplete"]["rustc"]["exit"] != 0
        assert fixture["rust_incomplete"]["blocks"][0]["complete"]
        assert not fixture["unclosed_annotation"]["blocks"][0]["complete"]
        assert fixture["unclosed_annotation"]["projection"] == "-- synthetic header\n"
        assert fixture["malformed_annotation_line"]["projection"] == "-- synthetic header\n"
        assert fixture["unsaved_buffer"]["projection"] != fixture["baseline"]["projection"]
        assert "retained spacing" in fixture["rust_body_changed"]["projection"]

        projected, _ = render(baseline)
        h_source, h_projection = sha(baseline), sha(projected)
        token = "exact helper"
        first = projected.index(token)
        helper = "trivial"
        second = projected.index(helper)
        good_edits = [
            {"range": [first, first + len(token)], "expected": token, "replacement": "exact True.intro"},
            {"range": [second, second + len(helper)], "expected": helper, "replacement": "exact True.intro"},
        ]
        actions = {
            "two_user_edits": apply_action(baseline, h_source, h_projection, 1, 1, good_edits),
            "synthetic_additional_edit": apply_action(baseline, h_source, h_projection, 1, 1, good_edits + [{"range": [0, 2], "expected": "--", "replacement": "xx"}]),
            "snippet_with_placeholder": apply_action(baseline, h_source, h_projection, 1, 1, [{"range": [first, first + len(token)], "expected": token, "replacement": "exact ${1:helper}", "format": "snippet"}]),
            "stale_after_unrelated_rust_edit": apply_action(changed_rust, h_source, h_projection, 1, 1, good_edits),
            "stale_version": apply_action(baseline, h_source, h_projection, 1, 2, good_edits),
            "stale_projection": apply_action(baseline, h_source, "0" * 64, 1, 1, good_edits),
        }
        assert actions["two_user_edits"]["ok"]
        assert all(not v["ok"] and v["source"] == (changed_rust if k == "stale_after_unrelated_rust_edit" else baseline) for k, v in actions.items() if k != "two_user_edits")

        lean_cases = {
            "ordered_helpers": "theorem helper : True := by trivial\ntheorem proof : True := by exact helper\n",
            "reversed_helpers": "theorem proof : True := by exact helper\ntheorem helper : True := by trivial\n",
            "name_collision": "theorem helper : True := by trivial\ntheorem helper : True := by trivial\n",
            "namespaced_independent": "namespace A\ntheorem helper : True := by trivial\nend A\nnamespace B\ntheorem helper : True := by trivial\nend B\n",
        }
        lean = {}
        for name, source in lean_cases.items():
            path = tmp / f"{name}.lean"
            path.write_text(source)
            lean[name] = {"source": source, "sha256": sha(source), "result": command([LEAN, path], tmp)}
        assert lean["ordered_helpers"]["result"]["exit"] == 0
        assert lean["reversed_helpers"]["result"]["exit"] != 0
        assert lean["name_collision"]["result"]["exit"] != 0
        assert lean["namespaced_independent"]["result"]["exit"] == 0

        result = {"environment": {"python": platform.python_version(), "platform": platform.platform(), "lean_version": command([LEAN, "--version"], tmp)["stdout"].strip(), "rustc_version": command([RUSTC, "--version"], tmp)["stdout"].strip()}, "fixtures": fixture, "actions": actions, "lean_layouts": lean}
        (HERE / "raw-results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        print(json.dumps({"fixture_count": len(fixture), "action_count": len(actions), "lean_layout_count": len(lean), "rust_incomplete_discovered": fixture["rust_incomplete"]["blocks"][0]["complete"], "rejected_actions": sum(not x["ok"] for x in actions.values())}, sort_keys=True))


if __name__ == "__main__":
    main()
