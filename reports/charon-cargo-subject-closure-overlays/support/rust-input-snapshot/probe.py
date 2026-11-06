#!/usr/bin/env python3
"""Offline Cargo input-closure and file-ownership controls at one rustc pin."""

import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "fixture"
TOOLCHAIN = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin")
OUT = HERE / "raw-results.json"


def digest_bytes(data):
    return hashlib.sha256(data).hexdigest()


def digest_file(path):
    return digest_bytes(Path(path).read_bytes())


def run(args, cwd, env=None, stdin=None):
    command = [str(x) for x in args]
    result = subprocess.run(command, cwd=cwd, env=env, input=stdin, text=True, capture_output=True)
    return {"command": command, "cwd_role": str(cwd.name), "exit_code": result.returncode,
            "stdout": result.stdout, "stderr": result.stderr}


def source_hashes(root):
    return {str(p.relative_to(root)): digest_file(p) for p in sorted(root.rglob("*"))
            if p.is_file() and "target" not in p.parts and ".cargo-home" not in p.parts}


def cargo_probe(scratch):
    root = scratch / "workspace"
    shutil.copytree(FIXTURE, root)
    target = scratch / "target"
    cargo_home = scratch / ".cargo-home"
    cargo_home.mkdir()
    env = dict(os.environ, RUSTC=str(TOOLCHAIN / "rustc"),
               CARGO_TARGET_DIR=str(target), CARGO_HOME=str(cargo_home))
    app = root / "app"
    main = app / "src/main.rs"
    note = app / "src/proof_note.txt"
    manifest = app / "Cargo.toml"
    lock = root / "Cargo.lock"
    base_source, base_note, base_manifest, base_lock = (p.read_bytes() for p in (main, note, manifest, lock))
    observations = []

    def build(label, extra=(), expect=None):
        result = run([TOOLCHAIN / "cargo", "run", "--offline", "--locked", "--quiet",
                      "-p", "snapshot_app", *extra], root, env)
        result.update({"label": label, "inputs_sha256": source_hashes(root),
                       "binary_sha256": digest_file(target / "debug/snapshot_app") if (target / "debug/snapshot_app").exists() else None})
        observations.append(result)
        if expect is not None:
            assert result["exit_code"] == 0 and result["stdout"].strip() == expect, (label, result)
        return result

    baseline = build("baseline", expect="macro=1 included=alpha feature=0")
    note.write_text("beta\n")
    note_changed = build("included-file-beta", expect="macro=1 included=beta feature=0")
    note.write_bytes(base_note)
    main.write_text(main.read_text().replace("proof: alpha", "proof: beta"))
    doc_changed = build("doc-comment-beta", expect="macro=2 included=alpha feature=0")
    main.write_bytes(base_source)
    reverted = build("doc-comment-revert-A", expect="macro=1 included=alpha feature=0")
    assert baseline["inputs_sha256"]["app/src/main.rs"] == reverted["inputs_sha256"]["app/src/main.rs"]
    assert baseline["stdout"] == reverted["stdout"] and doc_changed["stdout"] != baseline["stdout"]
    feature = build("cli-feature-selected", extra=("--features", "selected"),
                    expect="macro=1 included=alpha feature=10")
    manifest.write_text(manifest.read_text().replace("default = []", 'default = ["selected"]'))
    manifest_feature = build("manifest-default-selected", expect="macro=1 included=alpha feature=10")
    manifest.write_bytes(base_manifest)
    reverted_manifest = build("manifest-revert", expect="macro=1 included=alpha feature=0")
    lock.write_text(lock.read_text().replace('name = "doc_macro"\nversion = "0.1.0"',
                                             'name = "doc_macro"\nversion = "0.2.0"'))
    lock_rejected = build("stale-lockfile", expect=None)
    assert lock_rejected["exit_code"] != 0 and "cannot update the lock file" in lock_rejected["stderr"].lower(), lock_rejected
    lock.write_bytes(base_lock)
    assert main.read_bytes() == base_source and note.read_bytes() == base_note
    assert manifest.read_bytes() == base_manifest and lock.read_bytes() == base_lock
    return {"observations": observations, "toolchain": {
        "rustc": run([TOOLCHAIN / "rustc", "--version", "--verbose"], root),
        "cargo": run([TOOLCHAIN / "cargo", "--version"], root)},
        "assertions": {"included_file_changed_output_with_same_main":
            baseline["inputs_sha256"]["app/src/main.rs"] == note_changed["inputs_sha256"]["app/src/main.rs"]
            and baseline["stdout"] != note_changed["stdout"],
            "doc_comment_changed_proc_macro_output": baseline["stdout"] != doc_changed["stdout"],
            "source_A_B_A_hash_and_output": baseline["inputs_sha256"]["app/src/main.rs"]
                == reverted["inputs_sha256"]["app/src/main.rs"] and baseline["stdout"] == reverted["stdout"],
            "cli_feature_changes_output": baseline["stdout"] != feature["stdout"],
            "manifest_default_changes_output": baseline["stdout"] != manifest_feature["stdout"],
            "locked_rejects_stale_lock": lock_rejected["exit_code"] != 0,
            "manifest_revert_output": reverted_manifest["stdout"] == baseline["stdout"]}}


def overlay_probe(scratch):
    root = scratch / "overlay"
    root.mkdir()
    disk = root / "host.rs"
    disk_text = 'fn main() { println!("disk-A"); }\n'
    buffer_text = 'fn main() { println!("buffer-B"); }\n'
    disk.write_text(disk_text)
    disk_bin, buffer_bin = root / "disk-bin", root / "buffer-bin"
    disk_compile = run([TOOLCHAIN / "rustc", "--crate-name", "overlay_disk", "--edition=2021",
                        str(disk), "-o", str(disk_bin)], root)
    buffer_compile = run([TOOLCHAIN / "rustc", "--crate-name", "overlay_buffer", "--edition=2021",
                          "-", "-o", str(buffer_bin)], root, stdin=buffer_text)
    assert disk_compile["exit_code"] == buffer_compile["exit_code"] == 0
    disk_output, buffer_output = run([disk_bin], root), run([buffer_bin], root)
    assert disk_output["stdout"] == "disk-A\n" and buffer_output["stdout"] == "buffer-B\n"
    assert disk.read_text() == disk_text
    return {"disk_source_sha256": digest_bytes(disk_text.encode()),
            "unsaved_buffer_sha256": digest_bytes(buffer_text.encode()),
            "disk_compile": disk_compile, "buffer_compile": buffer_compile,
            "disk_run": disk_output, "buffer_run": buffer_output,
            "disk_unchanged_after_buffer_compile": disk.read_text() == disk_text}


def cas_probe(scratch):
    root = scratch / "ownership"
    root.mkdir()
    state = root / "state.json"
    guard = root / "guard.lock"
    state.write_text(json.dumps({"revision": 1, "content": "A"}))
    operations = []

    def cas(owner, expected_revision, expected_content_hash, new_content):
        with guard.open("a+") as lock_file:
            fcntl.flock(lock_file, fcntl.LOCK_EX)
            current = json.loads(state.read_text())
            accepted = (current["revision"] == expected_revision
                        and digest_bytes(current["content"].encode()) == expected_content_hash)
            if accepted:
                updated = {"revision": current["revision"] + 1, "content": new_content}
                staged = root / "state.next"
                staged.write_text(json.dumps(updated))
                os.replace(staged, state)
            after = json.loads(state.read_text())
            fcntl.flock(lock_file, fcntl.LOCK_UN)
        operations.append({"owner": owner, "expected_revision": expected_revision,
                           "expected_hash": expected_content_hash, "replacement": new_content,
                           "accepted": accepted, "state_after": after})
        return accepted

    hash_a, hash_b = digest_bytes(b"A"), digest_bytes(b"B")
    assert cas("editor", 1, hash_a, "B")
    assert not cas("agent-stale", 1, hash_a, "C")
    assert cas("editor-revert", 2, hash_b, "A")
    assert not cas("agent-ABA-stale", 1, hash_a, "C")
    current = json.loads(state.read_text())
    assert current == {"revision": 3, "content": "A"}
    hash_only_would_accept = digest_bytes(current["content"].encode()) == hash_a
    assert hash_only_would_accept
    return {"operations": operations, "final_state": current,
            "old_A_hash_matches_after_ABA": hash_only_would_accept,
            "revision_guard_rejects_old_A": not operations[-1]["accepted"]}


def main():
    with tempfile.TemporaryDirectory(prefix="anneal-rust-input-probe-", dir=HERE) as temp:
        scratch = Path(temp)
        output = {"environment": {"python": sys.version, "platform": platform.platform(),
                                  "script_sha256": digest_file(__file__),
                                  "fixture_sha256": source_hashes(FIXTURE)},
                  "cargo": cargo_probe(scratch),
                  "overlay": overlay_probe(scratch),
                  "ownership": cas_probe(scratch)}
    OUT.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"cargo_cases": len(output["cargo"]["observations"]),
                      "cargo_assertions": output["cargo"]["assertions"],
                      "overlay_outputs": [output["overlay"]["disk_run"]["stdout"].strip(),
                                          output["overlay"]["buffer_run"]["stdout"].strip()],
                      "ABA_hash_only_would_accept": output["ownership"]["old_A_hash_matches_after_ABA"]},
                     sort_keys=True))


if __name__ == "__main__":
    main()
