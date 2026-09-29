#!/usr/bin/env python3
"""Offline, read-only checker for the retained I094 installed-toolchain inventory."""
import hashlib
import json
from pathlib import Path
import shlex

from collect import HERE, TOOLS, REF, ELAN, NIX, RELEASE_PIN, SOURCE_PIN, V429, V430, NIX_V430

TIP = "40b3024d5a3c73357abb6e90f10fcaf713768cd4"
EXPECTED = {
    "$TOOLS/elan/toolchains/leanprover--lean4---v4.29.0/bin/lean": "2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37",
    "$TOOLS/elan/toolchains/leanprover--lean4---v4.29.0/bin/lake": "0e56506385ec20d56bffd7c031c4d48573ab5fdb74e5246ec8c45a220bebc68b",
    "$TOOLS/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean": "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997",
    "$TOOLS/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake": "9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb",
    "$NIX_STORE/wf1mr6pak9n88v5bwm6y749d8k19r0mw-lean-toolchain-aarch64-darwin-4.30.0-rc2/bin/lean": "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997",
    "$NIX_STORE/wf1mr6pak9n88v5bwm6y749d8k19r0mw-lean-toolchain-aarch64-darwin-4.30.0-rc2/bin/lake": "9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb",
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def command(argv):
    return shlex.join(map(str, argv))

def main():
    root = HERE.parent
    inv = json.loads((HERE / "inventory.json").read_text())
    meta = json.loads((root / "REPORT.json").read_text())
    assert inv["schema"] == 1 and inv["observed_at"] == meta["observed_at"] == "2026-09-29"
    rows = {x["label"]: x for x in inv["commands"]}
    assert len(rows) == len(inv["commands"]) == 7
    wanted = {
        "reference_tip": (command(["git", "rev-parse", "HEAD"]), str(REF), 0),
        "bundled_toolchain_directories": (command(["find", ELAN, "-mindepth", "1", "-maxdepth", "1", "-type", "d", "-print"]), None, 0),
        "home_elan_toolchain_directory": (command(["test", "-d", "/Users/josh/.elan/toolchains"]), None, 1),
        "nix_store_lean_named_directories": (command(["find", NIX, "-maxdepth", "1", "-type", "d", "-iname", "*lean*", "-print"]), None, 0),
        "installed_executable_hashes": (command(["shasum", "-a", "256", V429 / "lean", V429 / "lake", V430 / "lean", V430 / "lake", NIX_V430 / "lean", NIX_V430 / "lake"]), None, 0),
        "aeneas_release_pin": (command(["cat", RELEASE_PIN]), None, 0),
        "aeneas_source_pin": (command(["cat", SOURCE_PIN]), None, 0),
    }
    assert set(rows) == set(wanted)
    for label, row in rows.items():
        cmd, cwd, status = wanted[label]
        assert (row["command"], row["cwd"], row["exit"]) == (cmd, cwd, status)
        assert row["stdout_normalized_sha256"] == sha(row["stdout_normalized"].encode())
        assert row["stderr_normalized_sha256"] == sha(row["stderr_normalized"].encode())
        assert row["stderr_normalized"] == ""
    assert rows["reference_tip"]["stdout_normalized"] == TIP + "\n"
    assert set(rows["bundled_toolchain_directories"]["stdout_normalized"].splitlines()) == {
        "$TOOLS/elan/toolchains/leanprover--lean4---v4.29.0",
        "$TOOLS/elan/toolchains/leanprover--lean4---v4.30.0-rc2"}
    assert rows["home_elan_toolchain_directory"]["stdout_normalized"] == ""
    assert set(rows["nix_store_lean_named_directories"]["stdout_normalized"].splitlines()) == {
        "$NIX_STORE/afds973lgpak74wpp2apyj0zrnlb9h7w-leantar-aarch64-darwin-0.1.16",
        "$NIX_STORE/wf1mr6pak9n88v5bwm6y749d8k19r0mw-lean-toolchain-aarch64-darwin-4.30.0-rc2"}
    hashes = dict(line.split("  ", 1)[::-1] for line in rows["installed_executable_hashes"]["stdout_normalized"].splitlines())
    assert hashes == EXPECTED
    assert rows["aeneas_release_pin"]["stdout_normalized"] == "leanprover/lean4:v4.30.0-rc2\n"
    assert rows["aeneas_source_pin"]["stdout_normalized"] == rows["aeneas_release_pin"]["stdout_normalized"]
    subjects = {x["name"]: x["identity"] for x in meta["subjects"]}
    assert len(subjects) == len(meta["subjects"]) == 3
    assert subjects["I094 installed Lean/Lake inventory"]["reference_revision"] == TIP
    assert subjects["I094 installed Lean/Lake inventory"]["inventory_sha256"] == sha((HERE / "inventory.json").read_bytes())
    assert subjects["I094 installed Lean/Lake inventory"]["collector_sha256"] == sha((HERE / "collect.py").read_bytes())
    assert subjects["I094 installed Lean/Lake inventory"]["checker_sha256"] == sha((HERE / "check.py").read_bytes())
    bundled = subjects["Bundled and Nix Lean/Lake executables"]
    assert bundled == {
        "bundled_versions": "v4.29.0; v4.30.0-rc2",
        "nix_store_lean_toolchain_version": "v4.30.0-rc2",
        "lean_v429_sha256": EXPECTED["$TOOLS/elan/toolchains/leanprover--lean4---v4.29.0/bin/lean"],
        "lake_v429_sha256": EXPECTED["$TOOLS/elan/toolchains/leanprover--lean4---v4.29.0/bin/lake"],
        "lean_v430_rc2_sha256": EXPECTED["$TOOLS/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean"],
        "lake_v430_rc2_sha256": EXPECTED["$TOOLS/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake"],
    }
    pin = subjects["Pinned Aeneas Lean selection"]
    assert pin["lean_toolchain"] == rows["aeneas_release_pin"]["stdout_normalized"].strip()
    assert pin["release_pin_sha256"] == sha(rows["aeneas_release_pin"]["stdout_normalized"].encode())
    assert pin["source_pin_sha256"] == sha(rows["aeneas_source_pin"]["stdout_normalized"].encode())
    print("PASS: retained read-only commands, two bundled tuples, one matching Nix 4.30 tuple, Aeneas pin; no later installed candidate in inspected roots")

if __name__ == "__main__":
    main()
