#!/usr/bin/env python3
"""Record source/copied tree metadata and NAR hashes."""

import hashlib
import os
import re
import stat
import subprocess
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
TREES = {
    "lean_source": Path("/nix/store/wf1mr6pak9n88v5bwm6y749d8k19r0mw-lean-toolchain-aarch64-darwin-4.30.0-rc2"),
    "lean_copy": HERE / "relocated_lean",
    "rust_source": Path("/nix/store/ms2vns33wg2qxzqdfdw37w6g9xay9jjc-rust-toolchain-aarch64-darwin-2026-05-31"),
    "rust_copy": HERE / "relocated_rust",
}


def now():
    return datetime.now(timezone.utc).isoformat()


def run(log, label, argv, timeout=60):
    log.write(f"\n[{now()}] {label}: {' '.join(map(str, argv))}\n")
    try:
        p = subprocess.run(argv, text=True, capture_output=True, timeout=timeout)
        log.write(p.stdout + p.stderr)
        log.write(f"exit={p.returncode}\n")
        log.flush()
        return p.stdout, p.returncode == 0
    except subprocess.TimeoutExpired as e:
        log.write(f"TIMEOUT after {timeout}s: {e}\n")
        log.flush()
        return "", False


def health(log, label):
    dh, a = run(log, label, ["df", "-h", "/nix"])
    dk, b = run(log, label, ["df", "-k", "/nix"])
    mm, c = run(log, label, ["memory_pressure"])
    match = re.search(r"System-wide memory free percentage:\s*(\d+)%", mm)
    memory = int(match.group(1)) if match else -1
    try:
        disk = int(dk.strip().splitlines()[-1].split()[3])
    except (IndexError, ValueError):
        disk = -1
    log.write(f"resource_summary: memory_free={memory}% disk_available_kib={disk}\n")
    return a and b and c, memory, disk


def inventory(root, dest):
    rows = []
    pending = [root]
    while pending:
        path = pending.pop()
        st = path.lstat()
        rel = "." if path == root else str(path.relative_to(root))
        if stat.S_ISDIR(st.st_mode):
            kind = "dir"
            pending.extend(sorted(path.iterdir(), reverse=True))
        elif stat.S_ISLNK(st.st_mode):
            kind = "link"
        elif stat.S_ISREG(st.st_mode):
            kind = "file"
        else:
            kind = "other"
        link = os.readlink(path) if kind == "link" else ""
        rows.append((rel, kind, f"{stat.S_IMODE(st.st_mode):04o}", str(st.st_size), link))
    rows.sort(key=lambda r: r[0])
    dest.write_text("relative_path\ttype\tmode_octal\tsize_bytes\tsymlink_target\n" +
                    "".join("\t".join(r) + "\n" for r in rows))
    counts = Counter(row[1] for row in rows)
    executables = sum(row[1] == "file" and (int(row[2], 8) & 0o111) != 0 for row in rows)
    digest = hashlib.sha256(dest.read_bytes()).hexdigest()
    return rows, counts, executables, digest


with (HERE / "inventory.log").open("w") as log:
    log.write(f"started_utc={now()}\n")
    okay, memory, disk = health(log, "before inventory/hash")
    if not okay or memory < 35 or disk < 20 * 1024 * 1024:
        log.write("RESULT=SKIPPED_RESOURCE_GUARD\n")
        raise SystemExit(2)
    inventories = {}
    for name, path in TREES.items():
        rows, counts, executable_count, digest = inventory(path, HERE / f"inventory_{name}.tsv")
        inventories[name] = rows
        log.write(f"{name}: path={path} entries={len(rows)} counts={dict(counts)} executable_files={executable_count} inventory_sha256={digest}\n")
        command = (
            "source /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh && "
            "nix --extra-experimental-features 'nix-command flakes' hash path " + str(path)
        )
        digest_output, success = run(log, f"{name} NAR hash", ["/bin/bash", "-c", command])
        log.write(f"{name}: nar_hash={digest_output.strip() if success else 'ERROR'}\n")
    for kind in ("lean", "rust"):
        same = inventories[f"{kind}_source"] == inventories[f"{kind}_copy"]
        log.write(f"{kind}: source_copy_inventory_equal={same}\n")
    okay, memory, disk = health(log, "after inventory/hash")
    log.write(f"RESULT={'COMPLETE' if okay and memory >= 30 and disk >= 20 * 1024 * 1024 else 'STOP_RESOURCE_GUARD'}\n")
