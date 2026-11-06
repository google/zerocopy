#!/usr/bin/env python3
"""Real Charon/Aeneas provenance specimens plus an illustrative edit-authority model."""

import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
FROZEN = HERE / "frozen"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
RUST_BIN = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
RUST_LIB = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/lib"
CHARON = TOOLS / "bin/charon"
RUSTFMT = Path("/opt/homebrew/bin/rustfmt")
FORMATTED = HERE / "formatted-macro.rs"
FORMATTED_LLBC = HERE / "formatted-macro.llbc"


def sha(data):
    if isinstance(data, Path):
        data = data.read_bytes()
    if isinstance(data, str):
        data = data.encode()
    return hashlib.sha256(data).hexdigest()


def named_function(llbc, suffix):
    tr = llbc["translated"]
    hits = []
    for entry in tr["fun_decls"]:
        if not entry:
            continue
        name = entry["item_meta"].get("name", [])
        names = [part["Ident"][0] for part in name if "Ident" in part]
        if names and names[-1] == suffix:
            hits.append(entry)
    return hits


def charon_span(entry):
    m = entry["item_meta"]
    return {"def_id": entry["def_id"], "span": m["span"], "source_text": m.get("source_text"),
            "attributes": m.get("attr_info", {}).get("attributes", []), "is_local": m.get("is_local")}


def formatter_probe():
    original = (FROZEN / "macro-A.rs").read_bytes()
    FORMATTED.write_bytes(original)
    fmt = subprocess.run([str(RUSTFMT), str(FORMATTED)], capture_output=True, text=True, timeout=30)
    assert fmt.returncode == 0, fmt.stderr
    formatted = FORMATTED.read_bytes()
    FORMATTED_LLBC.unlink(missing_ok=True)
    env = dict(os.environ)
    env.update({"RUSTUP_HOME": str(TOOLS / "rustup"), "CARGO_HOME": str(TOOLS / "cargo"),
                "CHARON_TOOLCHAIN_IS_IN_PATH": "1",
                "PATH": os.pathsep.join([str(RUST_BIN), str(TOOLS / "bin"), env.get("PATH", "")]),
                "DYLD_LIBRARY_PATH": os.pathsep.join([str(RUST_LIB), str(RUST_LIB / "rustlib/aarch64-apple-darwin/lib"), env.get("DYLD_LIBRARY_PATH", "")])})
    command = [str(CHARON), "rustc", "--preset", "aeneas", "--dest-file", str(FORMATTED_LLBC), "--",
               str(FORMATTED), "--crate-type", "lib", "--crate-name", "subject_identity_probe", "--edition", "2021"]
    run = subprocess.run(command, cwd=HERE, env=env, capture_output=True, text=True, timeout=30)
    assert run.returncode == 0 and FORMATTED_LLBC.exists(), run.stderr
    before = json.loads((FROZEN / "macro-A.llbc").read_text())
    after = json.loads(FORMATTED_LLBC.read_text())
    assert before["has_errors"] is False and after["has_errors"] is False
    old_generated = [charon_span(x) for x in named_function(before, "generated")]
    new_generated = [charon_span(x) for x in named_function(after, "generated")]
    old_movable = [charon_span(x) for x in named_function(before, "movable")]
    new_movable = [charon_span(x) for x in named_function(after, "movable")]
    assert len(old_generated) == len(new_generated) == len(old_movable) == len(new_movable) == 1
    assert old_generated[0]["span"]["data"]["beg"]["line"] == 35
    assert new_generated[0]["span"]["data"]["beg"]["line"] == 47
    assert old_generated[0]["source_text"] is None and new_generated[0]["source_text"] is None
    assert old_movable[0]["span"]["data"]["beg"]["line"] == 41
    assert new_movable[0]["span"]["data"]["beg"]["line"] == 55
    return {"rustfmt_version": subprocess.check_output([str(RUSTFMT), "--version"], text=True).strip(),
            "charon_sha256": sha(CHARON), "rustfmt_sha256": sha(RUSTFMT),
            "original_source_sha256": sha(original), "formatted_source_sha256": sha(formatted),
            "original_llbc_sha256": sha(FROZEN / "macro-A.llbc"), "formatted_llbc_sha256": sha(FORMATTED_LLBC),
            "original_generated": old_generated[0], "formatted_generated": new_generated[0],
            "original_movable": old_movable[0], "formatted_movable": new_movable[0],
            "command": [s.replace(str(HERE), "$REPORT") for s in command],
            "exit": run.returncode, "stdout": run.stdout.replace(str(HERE), "$REPORT"),
            "stderr": run.stderr.replace(str(HERE), "$REPORT")}


def byte_positions(text):
    """Enumerate Unicode scalar boundaries and their byte/UTF-16 coordinates."""
    positions = []
    byte = 0
    line = 0
    scalar = 0
    utf16 = 0
    for char in text:
        positions.append({"byte": byte, "line": line, "scalar": scalar, "utf16": utf16})
        byte += len(char.encode("utf-8"))
        if char == "\n":
            line += 1
            scalar = utf16 = 0
        else:
            scalar += 1
            utf16 += len(char.encode("utf-16-le")) // 2
    positions.append({"byte": byte, "line": line, "scalar": scalar, "utf16": utf16})
    return positions


def inverse_utf16(positions, line, col):
    matches = [p["byte"] for p in positions if p["line"] == line and p["utf16"] == col]
    return matches[0] if len(matches) == 1 else None


def projection(source):
    """Invented /// payload syntax; exact authored bytes are its only edit authority."""
    out = "-- synthetic header\r\nnamespace Generated\r\n"
    segments = []
    offset = 0
    for line in source.splitlines(keepends=True):
        if line.startswith("/// ") and not line.startswith("/// ```"):
            payload = line[4:]
            start = len(out.encode("utf-8"))
            segments.append({"source": [offset + 4, offset + len(line.encode("utf-8"))],
                             "projected": [start, start + len(payload.encode("utf-8"))]})
            out += payload
        offset += len(line.encode("utf-8"))
    out += "end Generated\r\n"
    return out, segments


def edit_action(source, source_digest, projected_digest, edits, resources=()):
    out, segments = projection(source)
    source_bytes = source.encode("utf-8")
    out_bytes = out.encode("utf-8")
    if sha(source) != source_digest or sha(out) != projected_digest:
        return {"accepted": False, "reason": "stale-source-or-projection", "source": source}
    if resources:
        return {"accepted": False, "reason": "resource-operation-unsupported", "source": source}
    ranges = []
    for edit in edits:
        if edit["uri"] != "host.rs":
            return {"accepted": False, "reason": "read-only-or-external-uri", "source": source}
        a, b = edit["range"]
        exact = [s for s in segments if s["projected"][0] <= a < b <= s["projected"][1]]
        if len(exact) != 1:
            return {"accepted": False, "reason": "no-exact-single-origin", "source": source}
        seg = exact[0]
        lo = seg["source"][0] + a - seg["projected"][0]
        hi = seg["source"][0] + b - seg["projected"][0]
        expected = edit["expected"].encode("utf-8")
        if source_bytes[lo:hi] != expected or out_bytes[a:b] != expected:
            return {"accepted": False, "reason": "expected-text-mismatch", "source": source}
        ranges.append((lo, hi, edit["replacement"].encode("utf-8")))
    ordered = sorted(ranges)
    if any(ordered[i][1] > ordered[i + 1][0] for i in range(len(ordered) - 1)):
        return {"accepted": False, "reason": "overlap", "source": source}
    for lo, hi, replacement in reversed(ordered):
        source_bytes = source_bytes[:lo] + replacement + source_bytes[hi:]
    return {"accepted": True, "reason": "exact-atomic", "source": source_bytes.decode("utf-8")}


def projection_probe():
    host = ("pub fn item() {}\r\n"
            "/// ```lean\r\n"
            "/// theorem first : True := by exact True.intro -- 🧪 e\u0301\t\r\n"
            "/// theorem second : True := by exact True.intro\r\n"
            "/// ```\r\n")
    out, segments = projection(host)
    positions = byte_positions(out)
    assert len(segments) == 2
    host_valid_bytes = {p["byte"] for p in byte_positions(host)}
    projected_valid_bytes = {p["byte"] for p in positions}
    mapped_boundaries = 0
    host_raw, out_raw = host.encode("utf-8"), out.encode("utf-8")
    for segment in segments:
        s0, s1 = segment["source"]
        p0, p1 = segment["projected"]
        assert host_raw[s0:s1] == out_raw[p0:p1]
        for source_byte in host_valid_bytes:
            if s0 <= source_byte <= s1:
                projected_byte = p0 + source_byte - s0
                assert projected_byte in projected_valid_bytes
                assert s0 + projected_byte - p0 == source_byte
                mapped_boundaries += 1
    for p in positions:
        # CRLF positions at the start of LF are intentionally excluded from the inverse domain.
        if p["byte"] > 0 and out.encode()[p["byte"] - 1:p["byte"]] == b"\r":
            continue
        assert inverse_utf16(positions, p["line"], p["utf16"]) == p["byte"]
    inside_emoji = next(p for p in positions if out.encode()[p["byte"]:p["byte"] + 4] == "🧪".encode())
    assert inverse_utf16(positions, inside_emoji["line"], inside_emoji["utf16"] + 1) is None
    assert len("🧪".encode()) == 4
    assert inside_emoji["byte"] + 1 not in {p["byte"] for p in positions}
    first = out.encode("utf-8").index(b"True.intro")
    second = out.encode("utf-8").index(b"True.intro", first + 1)
    good = [{"uri": "host.rs", "range": [first, first + 10], "expected": "True.intro", "replacement": "trivial"},
            {"uri": "host.rs", "range": [second, second + 10], "expected": "True.intro", "replacement": "trivial"}]
    sd, pd = sha(host), sha(out)
    shifted = "// moved\r\n" + host
    cases = {
        "two_authored_ranges": edit_action(host, sd, pd, good),
        "synthetic_header": edit_action(host, sd, pd, good + [{"uri": "host.rs", "range": [0, 2], "expected": "--", "replacement": "xx"}]),
        "across_segments": edit_action(host, sd, pd, [{"uri": "host.rs", "range": [segments[0]["projected"][1] - 3, segments[1]["projected"][0] + 3], "expected": "x", "replacement": "y"}]),
        "generated_model_edit": edit_action(host, sd, pd, good + [{"uri": "Funs.lean", "range": [0, 2], "expected": "--", "replacement": "xx"}]),
        "rename_resource_op": edit_action(host, sd, pd, good, resources=("rename Funs.lean",)),
        "host_shift_same_projection": edit_action(shifted, sd, pd, good),
    }
    assert sha(projection(shifted)[0]) == pd
    assert cases["two_authored_ranges"]["accepted"]
    assert all(not v["accepted"] and v["source"] == (shifted if k == "host_shift_same_projection" else host)
               for k, v in cases.items() if k != "two_authored_ranges")
    return {"host": host, "host_sha256": sd, "projection": out, "projection_sha256": pd,
            "segments": segments, "coordinate_boundaries": len(positions), "exact_mapped_boundaries": mapped_boundaries,
            "different_numeric_columns": sum(p["scalar"] != p["utf16"] for p in positions),
            "emoji_start": inside_emoji, "invalid_surrogate_interior": [inside_emoji["line"], inside_emoji["utf16"] + 1],
            "cases": cases, "shifted_host_sha256": sha(shifted), "shifted_projection_sha256": sha(projection(shifted)[0])}


def aeneas_probe():
    source = (FROZEN / "snapshot.rs").read_text()
    generated = (FROZEN / "Funs.lean").read_text()
    llbc = json.loads((FROZEN / "snapshot.llbc").read_text())
    names = {n: [charon_span(x) for x in named_function(llbc, n)] for n in ("step", "select")}
    generated_comments = re.findall(r"/-- \[snapshot_probe::(\w+)\]:\s+Source: '([^']+)', lines ([^\n]+)\n", generated)
    assert len(generated_comments) == 2 and all(len(v) == 1 for v in names.values())
    assert set(n for n, _, _ in generated_comments) == set(names)
    # These joins are lexical/name/span candidates. No authenticated map is present.
    return {"source_sha256": sha(source), "llbc_sha256": sha(FROZEN / "snapshot.llbc"),
            "generated_sha256": sha(generated), "charon_items": names,
            "aeneas_comments": [{"name": n, "source_path": path, "display_span": span} for n, path, span in generated_comments],
            "candidate_edge_evidence": "lexical name/comment match only",
            "edit_authority_from_generated_comment": False}


def main():
    data = {"environment": {"platform": platform.platform(), "python": platform.python_version()},
            "formatter": formatter_probe(), "projection": projection_probe(), "aeneas": aeneas_probe(),
            "frozen_hashes": {p.name: sha(p) for p in sorted(FROZEN.iterdir()) if p.is_file()}}
    (HERE / "raw-results.json").write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"boundary_count": data["projection"]["coordinate_boundaries"],
                      "action_rejections": sum(not v["accepted"] for v in data["projection"]["cases"].values()),
                      "macro_old_line": data["formatter"]["original_generated"]["span"]["data"]["beg"]["line"],
                      "macro_formatted_line": data["formatter"]["formatted_generated"]["span"]["data"]["beg"]["line"]}, sort_keys=True))


if __name__ == "__main__":
    main()
