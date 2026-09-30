#!/usr/bin/env python3
"""Check R443's frozen claim and the static newer archive evidence offline."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import subprocess
from pathlib import Path


SUPPORT = Path(__file__).resolve().parent
ROOT = SUPPORT.parents[2]
E = json.loads((SUPPORT / "evidence.json").read_text())


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=ROOT)


def snapshot(path: str) -> bytes:
    return git("show", E["frozen_reference_commit"] + ":" + path)


def release_asset(tag: str) -> dict:
    release = json.loads((SUPPORT / f"{tag}-release.json").read_text())
    check(release["tag_name"] == tag, "release tag")
    name = f"lean-{tag[1:]}-linux_aarch64.tar.zst"
    matches = [x for x in release["assets"] if x["name"] == name]
    check(len(matches) == 1, "one official asset")
    return matches[0]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--raw-dir", type=Path, help="offline archive/helper bytes preserved in conversation Data")
    args = parser.parse_args()
    check(git("rev-parse", "HEAD").decode().strip() == E["frozen_reference_commit"], "wrong frozen parent")
    check(E["inventory_id"] == "R443", "inventory ID")
    check(E["baseline_inventory_commit"] == "ebcdcadb63fefd1e6c0f46cb2030270ae3232837", "inventory base")
    inventory_path = "reports/mathlib-430rc2-to-4341-cache-source-review/support/version-inventory-ebcdcad-581.csv"
    rows = list(csv.DictReader(snapshot(inventory_path).decode().splitlines()))
    check(len(rows) == 581, "frozen inventory count")
    original = rows[442]
    check(original["inventory_id"] == "R443", "frozen row position")
    check(json.loads((SUPPORT / "frozen-inventory-row.json").read_text()) == original, "exact frozen row")
    check(original["report_md_at_commit"] == E["predecessor_report_path"], "predecessor path")
    check(original["claim_or_cell_to_recheck"] == E["exact_frozen_claim"], "exact claim")
    for path, name, hash_field in (
        (original["report_md_at_commit"], "frozen-predecessor-REPORT.md", "predecessor_report_md_sha256"),
        (original["report_json_at_commit"], "frozen-predecessor-REPORT.json", "predecessor_report_json_sha256"),
        ("reports/lean-430-rc2-linux-aarch64-leantar-anomaly/support/archive-identities.json", "frozen-archive-identities.json", "predecessor_archive_identities_sha256"),
    ):
        data = (SUPPORT / name).read_bytes()
        check(data == snapshot(path), "frozen predecessor bytes: " + name)
        check(sha(data) == E[hash_field], "frozen predecessor hash: " + name)
    old_id = json.loads((SUPPORT / "frozen-archive-identities.json").read_text())
    check(old_id["lean_archive"]["sha256"] == E["old"]["archive_sha256"], "old archive digest")
    check(old_id["bundled_leantar"]["sha256"] == E["old"]["bundled_leantar_sha256"], "old helper digest")
    check(old_id["bundled_leantar"]["elf_e_machine"] == E["old"]["bundled_leantar_e_machine"] == 62, "old x86-64 header observation")
    check(E["old"]["evidence_status"] == "frozen_predecessor_not_redownloaded", "old evidence boundary")

    refs = (SUPPORT / "tag-refs.txt").read_text().splitlines()
    check(refs == [
        E["old"]["commit"] + "\trefs/tags/v4.30.0-rc2",
        E["new"]["commit"] + "\trefs/tags/v4.34.1",
    ], "official full tag refs")
    for side in ("old", "new"):
        value = E[side]
        asset = release_asset(value["tag"])
        check(asset["name"] == value["archive_name"], "asset name")
        check(asset["size"] == value["archive_size"], "asset size")
        check(asset["digest"] == "sha256:" + value["archive_sha256"], "official digest")
        if side == "new":
            check(asset["browser_download_url"] == value["archive_url"], "asset URL")

    for filename, identity in E["support_files"].items():
        data = (SUPPORT / filename).read_bytes()
        check(sha(data) == identity["sha256"] and len(data) == identity["size"], "support file hash: " + filename)
    check("17Gi" in (SUPPORT / "preflight.txt").read_text() and "61%" in (SUPPORT / "preflight.txt").read_text(), "preflight sample")
    check("16Gi" in (SUPPORT / "postdownload.txt").read_text() and "61%" in (SUPPORT / "postdownload.txt").read_text(), "post-download sample")
    check("curl_exit=0" in (SUPPORT / "budget-and-download.txt").read_text(), "bounded download exit")
    check(E["new"]["bundled_leantar_member"] in (SUPPORT / "member-list.txt").read_text(), "exact tar member")
    inspection = (SUPPORT / "helper-inspection.txt").read_text()
    check(E["new"]["bundled_leantar_sha256"] in inspection, "helper hash transcript")
    check("e_machine 183" in inspection and "ARM aarch64" in inspection, "ELF transcript")
    header = (SUPPORT / "new-bundled-leantar-elf-header.bin").read_bytes()
    check(len(header) == 64 and sha(header) == E["new"]["elf_header_sha256"], "ELF header snapshot")
    check(header[:4] == b"\x7fELF" and header[4:6] == b"\x02\x01", "ELF64 little endian")
    check(int.from_bytes(header[18:20], "little") == E["new"]["bundled_leantar_e_machine"] == 183, "new AArch64 machine")
    check(E["runtime_status"] == "unexecuted_static_binary_inspection_only", "runtime boundary")
    check(E["product_status"] == "unassessed" and E["nix_status"] == "not_invoked", "product and Nix bounds")

    if args.raw_dir:
        archive = args.raw_dir / E["new"]["archive_name"]
        helper = args.raw_dir / "bundled-leantar"
        check(archive.stat().st_size == E["new"]["archive_size"], "raw archive size")
        check(sha(archive.read_bytes()) == E["new"]["archive_sha256"], "raw archive digest")
        helper_bytes = helper.read_bytes()
        check(len(helper_bytes) == E["new"]["bundled_leantar_size"], "raw helper size")
        check(sha(helper_bytes) == E["new"]["bundled_leantar_sha256"], "raw helper digest")
        check(helper_bytes[:64] == header, "raw helper header")
        zstd = subprocess.Popen(["zstd", "-dc", str(archive)], stdout=subprocess.PIPE)
        extracted = subprocess.run(["tar", "-xOf", "-", E["new"]["bundled_leantar_member"]], stdin=zstd.stdout, stdout=subprocess.PIPE, check=True)
        assert zstd.stdout is not None
        zstd.stdout.close()
        check(zstd.wait() == 0, "archive stream exit")
        check(extracted.stdout == helper_bytes, "exact helper bytes from archive")
        print("PASS: frozen R443, official release metadata, raw archive digest, exact tar member, AArch64 ELF header; no execution")
    else:
        print("PASS: frozen R443, official release metadata, transcript hashes and AArch64 ELF header; raw archive not rehashed")


if __name__ == "__main__":
    main()
