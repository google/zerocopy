#!/usr/bin/env python3
"""Fetch or verify the exact official-document pages allowed by this run."""

from __future__ import annotations

import argparse
import csv
import hashlib
import html
import io
import re
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path


RUN = Path(__file__).resolve().parent
ALLOWLISTS = RUN / "freeze" / "allowlists"
MANIFEST = RUN / "freeze" / "authority-manifest.tsv"
MODES = ("S", "C", "X", "Q", "W", "M", "R", "K")
FIELDS = (
    "mode",
    "requested_url",
    "fetch_url",
    "final_url",
    "status",
    "content_type",
    "bytes",
    "sha256",
    "fragment_found",
    "retrieved_utc",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_pinned(path: Path) -> bytes:
    data = path.read_bytes()
    if (RUN / "freeze" / "LOCK.json").exists():
        import protocol

        if sha256(data) != protocol.frozen_file_digest(path):
            raise ValueError(f"frozen authority input changed while being read: {path}")
    return data


def load_urls() -> list[tuple[str, str]]:
    rows: list[tuple[str, str]] = []
    for mode in MODES:
        path = ALLOWLISTS / f"{mode}.txt"
        for url in read_pinned(path).decode().splitlines():
            if not re.fullmatch(r"https://doc\.rust-lang\.org/\S+", url):
                raise ValueError(f"invalid allowlisted URL: {url!r}")
            rows.append((mode, url))
    return rows


def without_fragment(url: str) -> str:
    parts = urllib.parse.urlsplit(url)
    return urllib.parse.urlunsplit((parts.scheme, parts.netloc, parts.path, parts.query, ""))


def fragment_present(requested_url: str, body: bytes) -> bool:
    fragment = urllib.parse.unquote(urllib.parse.urlsplit(requested_url).fragment)
    if not fragment:
        return True
    text = body.decode("utf-8", errors="replace")
    escaped = html.escape(fragment, quote=True)
    patterns = (
        rf'\bid=["\']{re.escape(fragment)}["\']',
        rf'\bid=["\']{re.escape(escaped)}["\']',
        rf'\bname=["\']{re.escape(fragment)}["\']',
    )
    return any(re.search(pattern, text) for pattern in patterns)


def fetch(url: str) -> dict[str, object]:
    request = urllib.request.Request(
        url,
        headers={"User-Agent": "unsafe-rust-skill-evaluation/1 authority-freeze"},
    )
    with urllib.request.urlopen(request, timeout=60) as response:
        body = response.read()
        return {
            "final_url": response.geturl(),
            "status": response.status,
            "content_type": response.headers.get_content_type(),
            "bytes": len(body),
            "sha256": sha256(body),
            "body": body,
            "retrieved_utc": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        }


def build_rows() -> list[dict[str, str]]:
    requested = load_urls()
    fetched: dict[str, dict[str, object]] = {}
    for _mode, requested_url in requested:
        fetch_url = without_fragment(requested_url)
        if fetch_url not in fetched:
            fetched[fetch_url] = fetch(fetch_url)

    rows: list[dict[str, str]] = []
    for mode, requested_url in requested:
        fetch_url = without_fragment(requested_url)
        result = fetched[fetch_url]
        found = fragment_present(requested_url, result["body"])
        if not found:
            raise ValueError(f"fragment not present in retrieved page: {requested_url}")
        rows.append(
            {
                "mode": mode,
                "requested_url": requested_url,
                "fetch_url": fetch_url,
                "final_url": str(result["final_url"]),
                "status": str(result["status"]),
                "content_type": str(result["content_type"]),
                "bytes": str(result["bytes"]),
                "sha256": str(result["sha256"]),
                "fragment_found": "true",
                "retrieved_utc": str(result["retrieved_utc"]),
            }
        )
    return rows


def render(rows: list[dict[str, str]]) -> str:
    output = io.StringIO(newline="")
    writer = csv.DictWriter(output, fieldnames=FIELDS, dialect="excel-tab", lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return output.getvalue()


def read_manifest() -> list[dict[str, str]]:
    rows = list(
        csv.DictReader(io.StringIO(read_pinned(MANIFEST).decode()), dialect="excel-tab")
    )
    if not rows or tuple(rows[0]) != FIELDS:
        raise ValueError("authority manifest has unexpected columns")
    return rows


def verify() -> None:
    rows = read_manifest()
    expected_pairs = load_urls()
    actual_pairs = [(row["mode"], row["requested_url"]) for row in rows]
    if actual_pairs != expected_pairs:
        raise ValueError("authority manifest does not match allowlist ordering")

    fetched: dict[str, dict[str, object]] = {}
    for row in rows:
        fetch_url = row["fetch_url"]
        if fetch_url != without_fragment(row["requested_url"]):
            raise ValueError(f"incorrect fetch URL for {row['requested_url']}")
        if fetch_url not in fetched:
            fetched[fetch_url] = fetch(fetch_url)
        result = fetched[fetch_url]
        checks = {
            "final_url": str(result["final_url"]),
            "status": str(result["status"]),
            "content_type": str(result["content_type"]),
            "bytes": str(result["bytes"]),
            "sha256": str(result["sha256"]),
        }
        for field, actual in checks.items():
            if row[field] != actual:
                raise ValueError(
                    f"authority drift for {row['requested_url']}: "
                    f"{field} frozen={row[field]!r} live={actual!r}"
                )
        if row["fragment_found"] != "true" or not fragment_present(
            row["requested_url"], result["body"]
        ):
            raise ValueError(f"fragment missing for {row['requested_url']}")
    print(f"verified {len(rows)} allowlist entries across {len(fetched)} pages")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="retrieve and write the frozen manifest")
    parser.add_argument(
        "--record-wave",
        type=int,
        choices=range(1, 6),
        help="verify live bytes and append a successful verification event for this collection wave",
    )
    args = parser.parse_args()
    if args.write and args.record_wave is not None:
        raise SystemExit("--write and --record-wave are mutually exclusive")
    if args.write:
        if (RUN / "freeze" / "LOCK.json").exists():
            raise SystemExit("refusing to rewrite authority manifest after freeze lock")
        MANIFEST.write_text(render(build_rows()))
        print(f"wrote {MANIFEST.relative_to(RUN)}")
    else:
        operation_lock_handle = None
        if args.record_wave is not None:
            import protocol

            operation_lock_handle = protocol.acquire_operation_lock()
            protocol.validate_static(require_lock=True, announce=False)
            protocol.assert_freeze_locked()
            protocol.assert_authority_verification_allowed(args.record_wave)
        verify()
        if args.record_wave is not None:
            protocol.append_event(
                "collection",
                "authority_verified",
                digest=protocol.frozen_file_digest(MANIFEST),
                details={"wave": args.record_wave, "entries": len(read_manifest())},
            )


if __name__ == "__main__":
    main()
