#!/usr/bin/env python3
"""Deterministic APFS tree-capture interleavings for issue #3731 I010."""
import hashlib
import json
import os
import platform
import shutil
import tempfile
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent
N_SOURCE = 256
N_OUTPUT = 32


def sha(data):
    return hashlib.sha256(data).hexdigest()


def payload(label, index):
    head = f"{label}:{index:03d}:".encode()
    return (head * (4096 // len(head) + 1))[:4096]


def write_file(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def make_tree(path, version):
    path.mkdir(parents=True)
    for i in range(N_SOURCE):
        if version == "B" and i == 200:
            name = "src/200-renamed.dat"
        else:
            name = f"src/{i:03d}.dat"
        data_version = "B" if version == "B" and i >= 128 else "A"
        write_file(path / name, payload(data_version, i))
    for i in range(N_OUTPUT):
        data_version = "B" if version == "B" and i == 10 else "A"
        write_file(path / f"generated/{i:03d}.bin", payload(data_version, i))
    write_file(path / "targets/alpha", b"alpha")
    write_file(path / "targets/beta", b"beta")
    (path / "link").symlink_to(f"targets/{'beta' if version == 'B' else 'alpha'}")


def inventory(path):
    result = {}
    for item in sorted(path.rglob("*")):
        rel = item.relative_to(path).as_posix()
        if item.is_symlink():
            result[rel] = {"kind": "symlink", "target": os.readlink(item)}
        elif item.is_file():
            result[rel] = {"kind": "file", "sha256": sha(item.read_bytes())}
    return result


def manifest_digest(items):
    return sha(json.dumps(items, sort_keys=True, separators=(",", ":")).encode())


def read_entries(path, names, midpoint, release, reached):
    entries = {}
    for index, name in enumerate(names):
        if index == midpoint:
            reached.set()
            assert release.wait(20), "writer gate timed out"
        item = path / name
        try:
            if item.is_symlink():
                entries[name] = {"kind": "symlink", "target": os.readlink(item)}
            else:
                entries[name] = {"kind": "file", "sha256": sha(item.read_bytes())}
        except FileNotFoundError:
            entries[name] = {"kind": "missing"}
    return entries


def trial(base, mode):
    generations = base / "generations"
    make_tree(generations / "A", "A")
    make_tree(generations / "B", "B")
    live = base / "live"
    shutil.copytree(generations / "A", live, symlinks=True)
    current = base / "current"
    current.symlink_to("generations/A")
    expected_a = inventory(generations / "A")
    expected_b = inventory(generations / "B")
    early = [f"src/{i:03d}.dat" for i in range(128)]
    names = early + [name for name in expected_a if name not in set(early)]
    midpoint = len(early)
    release = threading.Event()
    reached = threading.Event()
    outcome = {}

    def reader():
        if mode == "pinned":
            selected = (base / os.readlink(current)).resolve(strict=True)
        elif mode == "mutable-generation":
            selected = (base / os.readlink(current)).resolve(strict=True)
        else:
            selected = current
        outcome["selected"] = str(selected.relative_to(base)) if selected != current else "current/re-resolved"
        outcome["entries"] = read_entries(selected, names, midpoint, release, reached)

    thread = threading.Thread(target=reader)
    thread.start()
    assert reached.wait(20), "reader gate timed out"

    # These are actual filesystem edits, not a modeled event stream.
    write_file(live / "src/128.dat", payload("B", 128))
    (live / "src/200.dat").rename(live / "src/200-renamed.dat")
    replacement = live / "link-next"
    replacement.symlink_to("targets/beta")
    os.replace(replacement, live / "link")
    write_file(live / "generated/010.bin", payload("B", 10))
    if mode == "mutable-generation":
        write_file(generations / "A/src/220.dat", payload("M", 220))
    else:
        next_link = base / "current-next"
        next_link.symlink_to("generations/B")
        os.replace(next_link, current)
    release.set()
    thread.join(20)
    assert not thread.is_alive(), "reader did not finish"

    entries = outcome["entries"]
    outcome["matches_a"] = entries == expected_a
    outcome["matches_b"] = entries == expected_b
    outcome["manifest_digest"] = manifest_digest(entries)
    outcome["a_manifest_digest"] = manifest_digest(expected_a)
    outcome["b_manifest_digest"] = manifest_digest(expected_b)
    outcome["missing_names"] = [n for n, item in entries.items() if item["kind"] == "missing"]
    outcome["key_entries"] = {n: entries[n] for n in ("generated/010.bin", "link", "src/128.dat", "src/200.dat", "src/220.dat")}
    outcome["live_after"] = {
        "renamed_source_present": (live / "src/200-renamed.dat").exists(),
        "old_source_absent": not (live / "src/200.dat").exists(),
        "symlink_target": os.readlink(live / "link"),
        "output_hash": sha((live / "generated/010.bin").read_bytes()),
    }
    assert outcome["live_after"]["renamed_source_present"]
    assert outcome["live_after"]["old_source_absent"]
    assert outcome["live_after"]["symlink_target"] == "targets/beta"
    assert outcome["live_after"]["output_hash"] == sha(payload("B", 10))
    if mode == "pinned":
        assert outcome["matches_a"] and not outcome["matches_b"]
    elif mode == "re-resolved":
        assert not outcome["matches_a"] and not outcome["matches_b"]
        assert "src/200.dat" in outcome["missing_names"]
        assert outcome["key_entries"]["link"]["target"] == "targets/beta"
        assert outcome["key_entries"]["generated/010.bin"]["sha256"] == sha(payload("B", 10))
    else:
        assert not outcome["matches_a"] and not outcome["matches_b"]
        assert not outcome["missing_names"]
    return outcome


def main():
    scratch = os.environ.get("ANNEAL_PROBE_SCRATCH")
    with tempfile.TemporaryDirectory(prefix="i010-large-tree-", dir=scratch) as temporary:
        base = Path(temporary)
        trials = {}
        for mode in ("re-resolved", "pinned", "mutable-generation"):
            trials[mode] = trial(base / mode, mode)
    result = {
        "subject": "256 source files, 32 generated outputs, two target files, one symlink",
        "platform": platform.platform(),
        "python": platform.python_version(),
        "filesystem_probe": "local concurrent writer and reader threads with event gates",
        "trials": trials,
    }
    (ROOT / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({m: {"matches_a": t["matches_a"], "matches_b": t["matches_b"]} for m, t in trials.items()}, sort_keys=True))


if __name__ == "__main__":
    main()
